// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// fzn2smt — FlatZinc to SMT-LIB2 translation CLI and solver driver.
//
// Reads a .fzn file, translates constraints to SMT-LIB2 using the
// flatzinc-smt crate, and optionally pipes to z4 for solving with
// DZN-format output. This is the core executable for z4's MiniZinc
// Challenge entry.
//
// Commands:
//   translate <file.fzn>  — Print SMT-LIB2 translation to stdout
//   solve <file.fzn>      — Translate, solve with z4, output DZN
//   solve-cp <file.fzn>   — Solve with z4-cp engine directly, output DZN
//   info <file.fzn>       — Print model statistics (vars, constraints, objective)

use std::io::{self, Write};

use anyhow::{Context, Result};

mod solve;
mod solve_cp;

struct CliFlags {
    z4_bin: String,
    timeout_ms: Option<u64>,
    fd_search: bool,
    free_search_explicit: bool,
    all_solutions: bool,
    parallel_workers: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CliCommand {
    Translate,
    Solve,
    SolveCp,
    Info,
    AutoSolve,
}

/// Parse optional flags from CLI args, skipping command/file positions as needed.
/// Supports fzn2smt-native flags (--timeout, --fd-search) and
/// MiniZinc standard flags (-a, -f, -t, -p) advertised in z4.msc.
fn parse_flags(args: &[String], skip_positions: &[usize], allow_z4_bin: bool) -> Result<CliFlags> {
    let mut flags = CliFlags {
        z4_bin: "z4".to_string(),
        timeout_ms: None,
        fd_search: false,
        free_search_explicit: false,
        all_solutions: false,
        parallel_workers: 1,
    };
    let mut i = 1;
    while i < args.len() {
        if skip_positions.contains(&i) {
            i += 1;
            continue;
        }
        if let Some(val) = args[i].strip_prefix("--timeout=") {
            flags.timeout_ms = Some(
                val.parse::<u64>()
                    .with_context(|| format!("invalid --timeout value: {val}"))?,
            );
        } else if args[i] == "--timeout" || args[i] == "-t" {
            i += 1;
            while skip_positions.contains(&i) {
                i += 1;
            }
            let val = args.get(i).context("--timeout/-t requires a value")?;
            flags.timeout_ms = Some(
                val.parse::<u64>()
                    .with_context(|| format!("invalid timeout value: {val}"))?,
            );
        } else if args[i] == "--fd-search" {
            flags.fd_search = true;
        } else if args[i] == "-a" || args[i] == "--all-solutions" {
            flags.all_solutions = true;
        } else if args[i] == "-f" || args[i] == "--free-search" {
            // Free search = ignore search annotations. Explicitly disables
            // fd_search and prevents auto-activation from search annotations.
            flags.fd_search = false;
            flags.free_search_explicit = true;
        } else if args[i] == "-p" {
            i += 1; // consume the thread count argument
            while skip_positions.contains(&i) {
                i += 1;
            }
            let val = args.get(i).context("-p requires a value")?;
            flags.parallel_workers = val
                .parse::<usize>()
                .with_context(|| format!("invalid parallel worker count: {val}"))?;
            if flags.parallel_workers == 0 {
                anyhow::bail!("-p requires a positive worker count");
            }
        } else if args[i].starts_with('-') {
            eprintln!("warning: unknown flag '{}', ignoring", args[i]);
        } else if allow_z4_bin {
            flags.z4_bin = args[i].clone();
        } else {
            eprintln!(
                "warning: unexpected positional argument '{}', ignoring",
                args[i]
            );
        }
        i += 1;
    }
    Ok(flags)
}

fn parse_command(arg: &str) -> Option<CliCommand> {
    match arg {
        "translate" => Some(CliCommand::Translate),
        "solve" => Some(CliCommand::Solve),
        "solve-cp" => Some(CliCommand::SolveCp),
        "info" => Some(CliCommand::Info),
        _ => None,
    }
}

fn looks_like_fzn_input(arg: &str) -> bool {
    std::path::Path::new(arg)
        .extension()
        .and_then(|ext| ext.to_str())
        == Some("fzn")
}

fn activate_fd_search(flags: &mut CliFlags, result: &z4_flatzinc_smt::TranslationResult) {
    if !flags.free_search_explicit && !flags.fd_search && !result.search_annotations.is_empty() {
        flags.fd_search = true;
    }
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        print_usage();
        std::process::exit(1);
    }
    if matches!(args[1].as_str(), "-h" | "--help") {
        print_usage();
        return Ok(());
    }
    if matches!(args[1].as_str(), "-V" | "--version") {
        print_version();
        return Ok(());
    }

    let (command, fzn_path, mut flags) = if let Some(command) = parse_command(&args[1]) {
        if args.len() < 3 {
            print_usage();
            std::process::exit(1);
        }
        (
            command,
            args[2].clone(),
            parse_flags(&args, &[1, 2], matches!(command, CliCommand::Solve))?,
        )
    } else if looks_like_fzn_input(&args[1]) {
        (
            CliCommand::AutoSolve,
            args[1].clone(),
            parse_flags(&args, &[1], false)?,
        )
    } else if args[1].starts_with('-') {
        let Some(file_pos) = args
            .iter()
            .enumerate()
            .skip(2)
            .find_map(|(i, arg)| looks_like_fzn_input(arg).then_some(i))
        else {
            print_usage();
            std::process::exit(1);
        };
        (
            CliCommand::AutoSolve,
            args[file_pos].clone(),
            parse_flags(&args, &[file_pos], false)?,
        )
    } else {
        eprintln!("unknown command: {}", args[1]);
        print_usage();
        std::process::exit(1);
    };

    let input =
        std::fs::read_to_string(&fzn_path).with_context(|| format!("failed to read {fzn_path}"))?;

    let model = z4_flatzinc_parser::parse_flatzinc(&input)
        .map_err(|e| anyhow::anyhow!("parse error: {e}"))?;

    // The MiniZinc-facing entry path is a portfolio: prefer the CP backend
    // for FlatZinc models and fall back to the SMT backend when the CP
    // frontend reports unsupported constraints.
    if matches!(
        command,
        CliCommand::SolveCp | CliCommand::Solve | CliCommand::AutoSolve
    ) {
        let cp_unsupported = match command {
            CliCommand::Solve | CliCommand::AutoSolve => {
                match solve_cp::unsupported_constraints(&model) {
                    Ok(unsupported) => Some(unsupported),
                    Err(err) => {
                        eprintln!("warning: CP backend probe failed, falling back to SMT: {err}");
                        None
                    }
                }
            }
            CliCommand::SolveCp | CliCommand::Translate | CliCommand::Info => None,
        };
        let use_cp = match command {
            CliCommand::SolveCp => true,
            CliCommand::Solve | CliCommand::AutoSolve => {
                cp_unsupported.as_ref().is_some_and(Vec::is_empty)
            }
            CliCommand::Translate | CliCommand::Info => false,
        };
        if use_cp {
            return solve_cp::cmd_solve_cp(
                &model,
                flags.timeout_ms,
                flags.all_solutions,
                flags.parallel_workers,
                cp_unsupported.as_deref(),
            );
        }
    }

    let result = z4_flatzinc_smt::translate(&model)
        .map_err(|e| anyhow::anyhow!("translation error: {e}"))?;

    // Auto-activate branching search when the model has search annotations
    // and the user didn't explicitly request free search with -f.
    activate_fd_search(&mut flags, &result);

    match command {
        CliCommand::Translate => cmd_translate(&result),
        CliCommand::Solve | CliCommand::AutoSolve => solve::cmd_solve(
            &result,
            &flags.z4_bin,
            flags.timeout_ms,
            flags.fd_search,
            flags.all_solutions,
        ),
        CliCommand::Info => cmd_info(&model, &result),
        CliCommand::SolveCp => unreachable!("solve-cp returns before SMT translation"),
    }
}

fn print_usage() {
    println!("Usage: fzn2smt <command> <file.fzn> [options]");
    println!("   or: fzn2smt [options] <file.fzn>");
    println!();
    println!("General:");
    println!("  -h, --help                              Print this help message");
    println!("  -V, --version                           Print version information");
    println!();
    println!("Commands:");
    println!("  translate <file.fzn>                        Print SMT-LIB2 to stdout");
    println!(
        "  solve <file.fzn> [z4-path] [--timeout MS]   Auto-select CP/SMT backend, output DZN"
    );
    println!("  solve-cp <file.fzn> [--timeout MS]          Solve directly with z4-cp engine");
    println!("  info <file.fzn>                             Print model statistics");
    println!();
    println!("Default:");
    println!("  <file.fzn> [options]                        MiniZinc-compatible direct solve (prefers CP)");
    println!();
    println!("Options:");
    println!("  --timeout <ms>, -t <ms>   Per check-sat timeout in milliseconds");
    println!("  --fd-search               Force FD-track branching search");
    println!("  -a, --all-solutions       Enumerate all solutions (satisfaction)");
    println!("  -f, --free-search         Ignore search annotations (disable auto-FD)");
    println!("  -p <n>                    Parallel workers (solve-cp satisfaction only)");
}

fn print_version() {
    println!("fzn2smt {}", env!("CARGO_PKG_VERSION"));
}

/// Print the SMT-LIB2 translation to stdout.
fn cmd_translate(result: &z4_flatzinc_smt::TranslationResult) -> Result<()> {
    print!("{}", result.smtlib);
    io::stdout().flush()?;
    Ok(())
}

/// Print model statistics: variable count, constraint count, objective type.
fn cmd_info(
    model: &z4_flatzinc_parser::ast::FznModel,
    result: &z4_flatzinc_smt::TranslationResult,
) -> Result<()> {
    println!("=== FlatZinc Model Info ===");
    println!("Parameters:  {}", model.parameters.len());
    println!("Variables:   {}", model.variables.len());
    println!("Constraints: {}", model.constraints.len());
    println!("Output vars: {}", result.output_vars.len());
    match &result.objective {
        Some(obj) => {
            let dir = if obj.minimize { "minimize" } else { "maximize" };
            println!("Objective:   {dir} {}", obj.smt_expr);
        }
        None => println!("Objective:   satisfy"),
    }
    println!(
        "SMT-LIB2:   {} bytes, {} lines",
        result.smtlib.len(),
        result.smtlib.lines().count()
    );
    if result.search_annotations.is_empty() {
        println!("Search:      none (Free Search mode)");
    } else {
        println!(
            "Search:      {} annotation(s) (FD Search capable)",
            result.search_annotations.len()
        );
    }
    println!("Var domains: {} tracked", result.var_domains.len());
    Ok(())
}
