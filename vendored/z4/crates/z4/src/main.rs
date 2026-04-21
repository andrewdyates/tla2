// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 - A high-performance SMT solver in Rust
//!
//! Usage: z4 [OPTIONS] [FILE]

use std::env;
use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

/// Non-panicking replacement for `println!`. Avoids SIGABRT on broken stdout pipe.
macro_rules! safe_println {
    () => {{
        use std::io::Write;
        let _ = writeln!(std::io::stdout());
    }};
    ($($arg:tt)*) => {{
        use std::io::Write;
        let _ = writeln!(std::io::stdout(), $($arg)*);
    }};
}

/// Non-panicking replacement for `print!`. Avoids SIGABRT on broken stdout pipe.
macro_rules! safe_print {
    ($($arg:tt)*) => {{
        use std::io::Write;
        let _ = write!(std::io::stdout(), $($arg)*);
    }};
}

use z4_core::escape_string_contents;

mod chc_runner;
mod dimacs;
mod features;
mod run;
mod stats_output;
mod tracing_setup;

// Re-export is_horn_logic so tests in main_tests.rs can use `use super::*;`
#[cfg(test)]
use run::is_horn_logic;

/// Global timeout in milliseconds (0 = no timeout)
pub(crate) static GLOBAL_TIMEOUT_MS: AtomicU64 = AtomicU64::new(0);
pub(crate) static START_TIME: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
/// Global timeout flag — set by watchdog thread instead of process::exit (#2971).
/// All solve paths check this cooperatively and return Unknown/timeout.
static TIMED_OUT: AtomicBool = AtomicBool::new(false);
/// Shared interrupt handle for z4-dpll executor integration.
/// Set by the watchdog thread alongside TIMED_OUT.
pub(crate) static INTERRUPT_HANDLE: std::sync::OnceLock<Arc<AtomicBool>> =
    std::sync::OnceLock::new();
/// Whether periodic progress lines should be emitted to stderr.
/// Set by `--progress` CLI flag. Read by SAT, SMT, and CHC solve paths.
pub(crate) static PROGRESS_ENABLED: AtomicBool = AtomicBool::new(false);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChcMode {
    None,
    Chc,
    Portfolio,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExecutionMode {
    Interactive,
    PortfolioFile,
    AutoFile,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofFormat {
    Drat,
    Lrat,
    Alethe,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofConfig {
    pub(crate) path: String,
    pub(crate) format: ProofFormat,
    pub(crate) binary: bool,
}

impl ProofConfig {
    fn from_path(path: String) -> Self {
        let (format, binary) = infer_proof_format(&path);
        Self {
            path,
            format,
            binary,
        }
    }

    fn new(path: String, format: ProofFormat, binary: bool) -> Self {
        Self {
            path,
            format,
            binary,
        }
    }
}

fn infer_proof_format(path: &str) -> (ProofFormat, bool) {
    let ext = std::path::Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("");
    match ext {
        "drat" => (ProofFormat::Drat, false),
        "dratb" => (ProofFormat::Drat, true),
        "lrat" => (ProofFormat::Lrat, false),
        "lratb" => (ProofFormat::Lrat, true),
        "alethe" => (ProofFormat::Alethe, false),
        other => {
            safe_eprintln!(
                "c Warning: unknown proof extension '.{other}', defaulting to Alethe format"
            );
            (ProofFormat::Alethe, false)
        }
    }
}

/// Set global timeout in milliseconds
fn set_global_timeout(ms: u64) {
    // Z3 treats -t:0 as "no timeout" - honor that convention.
    if ms == 0 {
        env::remove_var("Z4_GLOBAL_TIMEOUT_MS");
        return;
    }
    GLOBAL_TIMEOUT_MS.store(ms, Ordering::SeqCst);
    env::set_var("Z4_GLOBAL_TIMEOUT_MS", ms.to_string());
    START_TIME.get_or_init(Instant::now);

    // Initialize the shared interrupt handle for z4-dpll integration.
    let handle = INTERRUPT_HANDLE.get_or_init(|| Arc::new(AtomicBool::new(false)));
    let watchdog_handle = handle.clone();

    // Spawn watchdog thread that signals timeout cooperatively (#2971).
    // Previous code called process::exit(124) which skips destructors and can
    // truncate in-progress DRAT/LRAT proofs and TLA traces. Now we set flags
    // that all solve paths check, allowing graceful shutdown.
    //
    // #5877: After the cooperative timeout fires, threads stuck in
    // non-interruptible computation (BvToBoolBitBlaster, ClauseInliner on
    // 10000-node BV transitions) can prevent process exit indefinitely.
    // Add a hard exit after a 2-second grace period as a safety net.
    std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(ms));
        TIMED_OUT.store(true, Ordering::SeqCst);
        watchdog_handle.store(true, Ordering::SeqCst);
        // Grace period for cooperative shutdown, then hard exit
        std::thread::sleep(Duration::from_secs(2));
        let _ = Write::write_all(&mut io::stderr(), b"unknown\n");
        let _ = Write::flush(&mut io::stderr());
        let _ = Write::write_all(&mut io::stdout(), b"unknown\n");
        let _ = Write::flush(&mut io::stdout());
        std::process::exit(124);
    });
}

/// Check whether the global timeout has fired. If so, print "timeout" and
/// exit with code 124.
///
/// NOTE: `process::exit` does NOT run Rust destructors on any thread (#3088).
/// We explicitly flush stdout/stderr to avoid truncated output. Proof file
/// writers (DRAT/LRAT, TLA traces) are not accessible here; they rely on the
/// cooperative timeout flag (TIMED_OUT / INTERRUPT_HANDLE) to flush and close
/// before the solver returns.
pub(crate) fn exit_if_timed_out() {
    if TIMED_OUT.load(Ordering::SeqCst) {
        safe_eprintln!("timeout");
        // Flush buffered I/O before process::exit skips destructors.
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(124);
    }
}

/// Returns true when the global watchdog timeout has fired.
pub(crate) fn is_timed_out() -> bool {
    TIMED_OUT.load(Ordering::Relaxed)
}

pub(crate) fn eprintln_smt_error(message: impl std::fmt::Display) {
    let message = message.to_string();
    safe_eprintln!("(error \"{}\")", escape_string_contents(&message));
}

// new_executor, execute_and_print, print_smt_stats, write_alethe_proof,
// run_interactive, run_file, is_horn_logic extracted to run.rs

/// Get elapsed time since process start.
pub(crate) fn global_elapsed() -> Duration {
    START_TIME.get().map_or(Duration::ZERO, Instant::elapsed)
}

/// Print CHC solve statistics to stderr.
///
/// When `chc_stats` is provided, populates the canonical stats envelope with
/// CHC-specific counters under the `chc.*` key namespace. Problem-level
/// counters (`chc.predicates`, `chc.clauses`) are always emitted.
pub(crate) fn print_chc_stats(
    start: &Instant,
    result: &str,
    engine: &str,
    stats_cfg: stats_output::StatsConfig,
    chc_stats: Option<&z4::chc::ChcStatistics>,
    num_predicates: u64,
    num_clauses: u64,
) {
    let elapsed = start.elapsed();
    if stats_cfg.human {
        safe_eprintln!(
            "(:chc-statistics\n  :result {result}\n  :engine {engine}\n  :time {:.3})",
            elapsed.as_secs_f64()
        );
    }

    // Canonical envelope
    let mode = if engine == "portfolio" {
        stats_output::SolveMode::Portfolio
    } else {
        stats_output::SolveMode::Chc
    };
    let mut run_stats = stats_output::RunStatistics::new(mode, result, global_elapsed());

    // Problem-level counters (always available).
    run_stats.insert("chc.predicates", num_predicates);
    run_stats.insert("chc.clauses", num_clauses);

    // Populate CHC-specific counters from engine statistics.
    if let Some(stats) = chc_stats {
        run_stats.insert("chc.iterations", stats.iterations);
        run_stats.insert("chc.lemmas_learned", stats.lemmas_learned);
        run_stats.insert("chc.max_frame", stats.max_frame);
        run_stats.insert("chc.restarts", stats.restarts);
        run_stats.insert("chc.smt_unknowns", stats.smt_unknowns);
        run_stats.insert("chc.cache_hits", stats.cache_hits);
        run_stats.insert("chc.cache_model_rejections", stats.cache_model_rejections);
        run_stats.insert("chc.cache_solver_calls", stats.cache_solver_calls);
    }

    run_stats.emit(stats_cfg);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    // Parse Z3-compatible flags and Z4 flags
    let mut verbose = false;
    let mut stats = false;
    let mut stats_json = false;
    let mut progress = false;
    let mut timeout_ms: Option<u64> = None;
    let mut memory_limit_mb: Option<u64> = None;
    let mut chc_mode = ChcMode::None;
    let mut file_arg: Option<String> = None;
    let mut stdin_mode = false;
    let mut incremental = false;
    let mut validate = false;
    let mut replay_trace_file: Option<String> = None;
    let mut proof_path: Option<String> = None;
    let mut proof_config_explicit: Option<ProofConfig> = None;

    let mut i = 1;
    while i < args.len() {
        let arg = &args[i];
        if arg == "--help" || arg == "-h" {
            print_help();
            return;
        } else if arg == "--version" || arg == "-v" {
            print_version();
            return;
        } else if arg == "--features" {
            features::print_feature_report();
            return;
        } else if arg == "--chc" {
            chc_mode = ChcMode::Chc;
        } else if arg == "--portfolio" {
            chc_mode = ChcMode::Portfolio;
        } else if arg == "--verbose" {
            verbose = true;
        } else if arg == "--validate" {
            validate = true;
        } else if arg == "--progress" {
            progress = true;
        } else if arg == "--stats" || arg == "-st" {
            stats = true;
        } else if arg == "--stats-json" {
            stats_json = true;
        } else if arg == "--proof" {
            if i + 1 >= args.len() {
                safe_eprintln!("Error: --proof requires a file path");
                std::process::exit(1);
            }
            i += 1;
            proof_path = Some(args[i].clone());
        } else if arg == "--drat"
            || arg == "--drat-binary"
            || arg == "--lrat"
            || arg == "--lrat-binary"
        {
            if i + 1 >= args.len() {
                safe_eprintln!("Error: {} requires a file path", arg);
                std::process::exit(1);
            }
            let format = if arg.starts_with("--drat") {
                ProofFormat::Drat
            } else {
                ProofFormat::Lrat
            };
            let binary = arg.ends_with("-binary");
            i += 1;
            proof_config_explicit = Some(ProofConfig::new(args[i].clone(), format, binary));
        } else if arg == "--replay" {
            if i + 1 >= args.len() {
                safe_eprintln!("Error: --replay requires a trace file path");
                std::process::exit(1);
            }
            i += 1;
            replay_trace_file = Some(args[i].clone());
        } else if arg == "-smt2" {
            // Z3 compatibility: accept -smt2 as no-op (we auto-detect)
        } else if arg == "-in" {
            // Z3 compatibility: read from stdin
            stdin_mode = true;
        } else if arg == "--incremental" {
            // Force line-by-line stdin processing even when piped (#5360).
            // Required by consumers (e.g., MiniZinc IncrementalSolver) that
            // send commands incrementally via pipe and read responses.
            stdin_mode = true;
            incremental = true;
        } else if let Some(timeout_str) = arg.strip_prefix("-t:") {
            // Z3 compatibility: -t:N sets timeout in milliseconds
            // Note: Z3 treats -t:0 as "no timeout"
            if let Ok(ms) = timeout_str.parse::<u64>() {
                // Preserve `-t:0` so CHC/portfolio mode can disable its internal budget.
                timeout_ms = Some(ms);
            } else {
                safe_eprintln!("Error: Invalid timeout value in {}", arg);
                std::process::exit(1);
            }
        } else if let Some(mem_str) = arg.strip_prefix("-memory:") {
            // Z3 compatibility: -memory:N sets memory limit in megabytes
            if let Ok(mb) = mem_str.parse::<u64>() {
                memory_limit_mb = Some(mb);
            } else {
                safe_eprintln!("Error: Invalid memory limit value in {}", arg);
                std::process::exit(1);
            }
        } else if arg.starts_with("fp.") || arg.contains('=') {
            // Z3 compatibility: accept fp.engine=spacer and similar options as no-op
            // Z4 auto-selects the CHC engine based on logic detection
        } else if arg.starts_with('-') {
            safe_eprintln!("Unknown option: {}", arg);
            print_help();
            std::process::exit(1);
        } else {
            file_arg = Some(arg.clone());
        }
        i += 1;
    }

    // Explicit --drat/--lrat flags take precedence over --proof (extension-inferred).
    let proof_config = proof_config_explicit.or_else(|| proof_path.map(ProofConfig::from_path));

    if let Some(trace_file) = replay_trace_file {
        env::set_var("Z4_REPLAY_TRACE_FILE", trace_file);
    }

    // Honor Z4_STATS env var (same as --stats flag)
    if !stats && env::var("Z4_STATS").is_ok() {
        stats = true;
    }

    // Build unified stats config from flags
    let stats_cfg = stats_output::StatsConfig {
        human: stats,
        json: stats_json,
    };

    // Store progress flag for solver configuration.
    if progress {
        PROGRESS_ENABLED.store(true, Ordering::SeqCst);
    }

    // Initialize wall-clock start time for stats envelope.
    START_TIME.get_or_init(Instant::now);

    // Set global timeout if specified
    if let Some(ms) = timeout_ms {
        set_global_timeout(ms);
    }

    // Set process-wide memory limit.
    // Priority: -memory:N flag > Z4_MEMORY_LIMIT env > auto-detect from physical RAM.
    // The limit applies to all solve paths (SMT, SAT, CHC) via z4_sys globals
    // checked by TermStore::global_memory_exceeded() and z4-dpll preflight.
    let memory_limit_bytes = if let Some(mb) = memory_limit_mb {
        if mb == 0 {
            0 // Explicit disable
        } else {
            (mb as usize) * 1024 * 1024
        }
    } else if let Ok(env_mb) = env::var("Z4_MEMORY_LIMIT") {
        env_mb
            .parse::<usize>()
            .map(|mb| mb * 1024 * 1024)
            .unwrap_or_else(|_| z4_sys::default_memory_limit())
    } else {
        z4_sys::default_memory_limit()
    };
    if memory_limit_bytes > 0 {
        z4_sys::set_process_memory_limit(memory_limit_bytes);
    }

    // Install tracing subscriber (no-op when verbose is false)
    tracing_setup::setup_tracing(verbose);

    // Decide what mode to run
    match determine_execution_mode(stdin_mode, file_arg.as_ref(), chc_mode) {
        ExecutionMode::Interactive => {
            run::run_interactive(stats_cfg, proof_config.as_ref(), incremental)
        }
        ExecutionMode::PortfolioFile => {
            if let Some(f) = file_arg {
                chc_runner::run_portfolio(
                    &f,
                    verbose,
                    validate,
                    timeout_ms,
                    stats_cfg,
                    proof_config.as_ref(),
                );
            }
        }
        ExecutionMode::AutoFile => {
            if let Some(f) = file_arg {
                run::run_file(&f, stats_cfg, proof_config.as_ref());
            }
        }
    }

    // Final timeout check: if the watchdog fired during output, exit 124 now.
    // This runs on the main thread so all destructors execute cleanly (#2971).
    exit_if_timed_out();
}

fn determine_execution_mode(
    stdin_mode: bool,
    file_arg: Option<&String>,
    chc_mode: ChcMode,
) -> ExecutionMode {
    if stdin_mode {
        return ExecutionMode::Interactive;
    }

    if file_arg.is_none() {
        return ExecutionMode::Interactive;
    }

    match chc_mode {
        ChcMode::None => ExecutionMode::AutoFile,
        // Keep `--chc` and `--portfolio` as aliases to preserve benchmark behavior.
        ChcMode::Chc | ChcMode::Portfolio => ExecutionMode::PortfolioFile,
    }
}

fn print_help() {
    safe_println!("Z4 - A high-performance SMT solver in Rust");
    safe_println!();
    safe_println!("Usage: z4 [OPTIONS] [FILE]");
    safe_println!();
    safe_println!("Options:");
    safe_println!("  -h, --help          Print this help message");
    safe_println!("  -v, --version       Print version information");
    safe_println!("  --features          Print build features, supported logics, and proof formats (JSON)");
    safe_println!("  --chc               Force CHC mode for FILE or stdin");
    safe_println!("  --portfolio         Alias for --chc");
    safe_println!("  --verbose           Enable verbose output (for --chc/--portfolio)");
    safe_println!("  --validate          Enable runtime result validation (for --chc/--portfolio)");
    safe_println!("  --progress          Print periodic progress lines to stderr (~5s)");
    safe_println!("  -st, --stats        Print solver statistics to stderr after solving");
    safe_println!("  --stats-json        Print solver statistics as JSON to stderr after solving");
    safe_println!("  --replay FILE       Replay SAT decision trace from FILE");
    safe_println!(
        "  --incremental       Line-by-line stdin even when piped (for incremental solvers)"
    );
    safe_println!();
    safe_println!("Proof certificates:");
    safe_println!("  --proof FILE        Write proof certificate to FILE on UNSAT (format from extension):");
    safe_println!("                        .drat    DRAT text proof");
    safe_println!("                        .dratb   DRAT binary proof");
    safe_println!("                        .lrat    LRAT text proof (recommended)");
    safe_println!("                        .lratb   LRAT binary proof");
    safe_println!("                        .alethe  Alethe SMT proof");
    safe_println!("  --drat FILE         Write DRAT proof to FILE on UNSAT");
    safe_println!("  --drat-binary FILE  Write DRAT binary proof to FILE on UNSAT");
    safe_println!("  --lrat FILE         Write LRAT proof to FILE on UNSAT");
    safe_println!("  --lrat-binary FILE  Write LRAT binary proof to FILE on UNSAT");
    safe_println!();
    safe_println!("  Clause ID tracking is always-on internally (zero overhead when no proof");
    safe_println!("  file is requested). LRAT proofs are reconstructed backward from the empty");
    safe_println!("  clause on UNSAT via deferred reconstruction.");
    safe_println!("  DRAT/LRAT proofs are verified by the built-in z4-drat-check / z4-lrat-check.");
    safe_println!("  DRAT/LRAT apply to DIMACS CNF (SAT); Alethe applies to SMT-LIB.");
    safe_println!("  CHC mode emits invariant/counterexample certificates on stdout (no --proof needed).");
    safe_println!();
    safe_println!("Z3-compatible options:");
    safe_println!("  -smt2               SMT-LIB 2 format (accepted, auto-detected)");
    safe_println!("  -in                 Read from stdin");
    safe_println!("  -t:N                Timeout in milliseconds");
    safe_println!("  -memory:N           Memory limit in megabytes (default: 50% of physical RAM)");
    safe_println!("  -st                 Print statistics (Z3 compatible)");
    safe_println!("  fp.engine=spacer    CHC engine selection (accepted, auto-selected)");
    safe_println!();
    safe_println!("File format auto-detection:");
    safe_println!("  .cnf / 'p cnf'      DIMACS CNF (SAT competition format)");
    safe_println!("  (set-logic HORN)    CHC (Horn clauses, PDR/IC3 solver)");
    safe_println!("  Otherwise           SMT-LIB 2.6");
    safe_println!();
    safe_println!("Result validation:");
    safe_println!("  Portfolio mode validates all results: Safe results are checked against");
    safe_println!("  clauses, Unsafe results are verified via counterexample traces.");
    safe_println!("  Validation failures return 'unknown' instead of wrong answers.");
    safe_println!();
    safe_println!("Z3-equivalent usage:");
    safe_println!("  echo \"$SMT\" | z4 -smt2 -in fp.engine=spacer -t:60000");
    safe_println!();
    safe_println!("If no file is given, runs in interactive mode.");
}

fn print_version() {
    safe_println!("{}", features::version_line());
}

#[cfg(test)]
#[path = "main_tests.rs"]
mod tests;
