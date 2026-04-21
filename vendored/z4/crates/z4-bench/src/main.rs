// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! # z4-bench — Competition-Standard Benchmarking for Z4
//!
//! Single CLI for running benchmarks and producing scores using the exact
//! scoring methods from SAT Competition, SMT-COMP, and CHC-COMP.
//!
//! ## Quick start
//!
//! ```bash
//! # Run all CHC benchmarks with dev timeout (fast)
//! z4-bench run --domain chc
//!
//! # Run all benchmarks with competition-standard timeouts
//! z4-bench run --all --competition
//!
//! # Score an existing results file
//! z4-bench score results.json --scoring sat-comp
//!
//! # List registered evals and their competition domains
//! z4-bench list
//!
//! # Print competition scoring methodology
//! z4-bench standards
//! ```

mod environment;
mod native;
mod runner;
mod scoring;

use clap::{Parser, Subcommand, ValueEnum};
use std::path::PathBuf;

/// Competition-standard benchmarking CLI for Z4 SMT solver.
///
/// Runs benchmarks and produces scores using the exact methods from:
///   SAT Competition — PAR-2 (penalized avg runtime, factor 2)
///   SMT-COMP       — lexicographic <errors, solved, wall-clock, cpu-time>
///   CHC-COMP       — solved count with CPU time tiebreaker
///
/// Two modes:
///   dev (default)   — short timeouts for fast iteration
///   --competition   — standard timeouts matching official rules
///
/// The scoring formula is always competition-standard. Only timeouts differ.
#[derive(Parser)]
#[command(name = "z4-bench", version, about, long_about = None)]
#[command(propagate_version = true)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Run benchmarks and produce competition-standard scores.
    ///
    /// By default uses short dev timeouts for fast iteration.
    /// Pass --competition to use official competition timeouts:
    ///   SAT-COMP: 5000s, SMT-COMP: 1200s, CHC-COMP: 1800s
    ///
    /// Examples:
    ///   z4-bench run --all                      # all evals, dev timeouts
    ///   z4-bench run --all --competition         # all evals, standard timeouts
    ///   z4-bench run --domain chc                # CHC evals only
    ///   z4-bench run --domain smt --competition  # SMT evals, 1200s timeout
    ///   z4-bench run chccomp-2025-extra-small-lia
    Run {
        /// Eval IDs to run (e.g., chccomp-2025-extra-small-lia, smt-smtcomp-qf-lia)
        eval_ids: Vec<String>,

        /// Run all registered evals
        #[arg(long)]
        all: bool,

        /// Run all evals for a specific competition domain
        #[arg(long, value_enum)]
        domain: Option<Domain>,

        /// Use competition-standard timeouts (SAT:5000s, SMT:1200s, CHC:1800s)
        #[arg(long)]
        competition: bool,

        /// Path to Z4 binary [default: target/release/z4]
        #[arg(long, default_value = "target/release/z4")]
        z4: PathBuf,

        /// Override timeout for all evals (seconds)
        #[arg(long)]
        timeout: Option<f64>,

        /// Write combined scorecard JSON to this path
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Number of runs per benchmark (median selected for statistical reliability)
        #[arg(long, default_value = "1")]
        runs: u32,

        /// Reference solver binary for comparison (e.g., z3). Runs on every
        /// benchmark after Z4 and reports agreement/disagreement.
        #[arg(long)]
        reference_solver: Option<PathBuf>,

        /// Minimal output
        #[arg(short, long)]
        quiet: bool,
    },

    /// Score an existing results JSON file using competition-standard scoring.
    ///
    /// Reads a results.json produced by z4-bench run,
    /// and applies the correct scoring formula.
    ///
    /// Examples:
    ///   z4-bench score results.json --scoring sat-comp
    ///   z4-bench score results.json --scoring smt-comp --division QF_LIA
    ///   z4-bench score results.json --scoring chc-comp --track LIA-Lin
    ///   z4-bench score results.json --scoring chc-comp --timeout 60
    Score {
        /// Path to results JSON file
        results_file: PathBuf,

        /// Competition scoring method to apply
        #[arg(long, value_enum)]
        scoring: ScoringMethod,

        /// Timeout used during the run (seconds). Competition default if omitted.
        #[arg(long)]
        timeout: Option<f64>,

        /// SMT-COMP division name (e.g., QF_LIA, QF_BV)
        #[arg(long)]
        division: Option<String>,

        /// CHC-COMP track name (e.g., LIA-Lin, LIA-Nonlin)
        #[arg(long)]
        track: Option<String>,

        /// Mark as competition-standard (asserts standard timeout was used)
        #[arg(long)]
        standard: bool,

        /// Output full score as JSON
        #[arg(long)]
        json: bool,
    },

    /// List all registered evals with their competition domain, scoring method, and timeouts.
    ///
    /// Reads eval specs from evals/registry/*.yaml.
    List,

    /// Print competition scoring methodology reference.
    ///
    /// Shows the exact scoring formulas, timeouts, and ranking criteria
    /// for SAT Competition, SMT-COMP, and CHC-COMP.
    Standards,
}

#[derive(Clone, ValueEnum)]
enum Domain {
    /// SAT Competition benchmarks (PAR-2 scoring)
    Sat,
    /// SMT-COMP benchmarks (lexicographic scoring per division)
    Smt,
    /// CHC-COMP benchmarks (solved count + CPU tiebreaker)
    Chc,
}

impl std::fmt::Display for Domain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Domain::Sat => write!(f, "sat"),
            Domain::Smt => write!(f, "smt"),
            Domain::Chc => write!(f, "chc"),
        }
    }
}

#[derive(Clone, ValueEnum)]
enum ScoringMethod {
    /// SAT Competition PAR-2: sum(wall_time if solved, 2*timeout if unsolved)
    SatComp,
    /// SMT-COMP lexicographic: <errors, solved, wall-clock, cpu-time>
    SmtComp,
    /// CHC-COMP: solved count, tiebreak by CPU time
    ChcComp,
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Run {
            eval_ids,
            all,
            domain,
            competition,
            z4,
            timeout,
            output,
            runs,
            reference_solver,
            quiet,
        } => runner::cmd_run(runner::RunArgs {
            eval_ids,
            all,
            domain: domain.map(|d| d.to_string()),
            competition,
            z4,
            timeout,
            output,
            runs,
            reference_solver,
            quiet,
        }),
        Commands::Score {
            results_file,
            scoring,
            timeout,
            division,
            track,
            standard,
            json,
        } => {
            let method = match scoring {
                ScoringMethod::SatComp => scoring::Competition::SatComp,
                ScoringMethod::SmtComp => scoring::Competition::SmtComp,
                ScoringMethod::ChcComp => scoring::Competition::ChcComp,
            };
            scoring::cmd_score(scoring::ScoreArgs {
                results_file,
                method,
                timeout,
                division,
                track,
                standard,
                json,
            })
        }
        Commands::List => runner::cmd_list(),
        Commands::Standards => {
            scoring::print_standards();
            Ok(())
        }
    };

    if let Err(e) = result {
        eprintln!("error: {e:#}");
        std::process::exit(1);
    }
}
