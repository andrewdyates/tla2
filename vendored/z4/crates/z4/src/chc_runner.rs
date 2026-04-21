// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CHC solver entry points and portfolio budget management.
//!
//! Extracted from `main.rs` as part of code-health module split.
//! Contains CHC content/file solving, portfolio execution, and time budget computation.

use super::{
    eprintln_smt_error, exit_if_timed_out, print_chc_stats, stats_output, ProofConfig,
    GLOBAL_TIMEOUT_MS, PROGRESS_ENABLED, START_TIME,
};
use std::env;
use std::fs;
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

/// Run CHC solver on content string.
///
/// Routes through `AdaptivePortfolio` to ensure all results are verified
/// via the `VerifiedChcResult` pipeline (#5811, #5747).
pub(crate) fn run_chc_from_content(
    content: &str,
    verbose: bool,
    validate: bool,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    use z4::chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

    // proof_config accepted but not yet used for file output — certificates are
    // always printed to stdout after the sat/unsat line (#8152).
    let _ = proof_config;

    let solve_start = Instant::now();

    let problem = match ChcParser::parse(content) {
        Ok(p) => p,
        Err(e) => {
            eprintln_smt_error(format_args!("Parse error: {e}"));
            std::process::exit(1);
        }
    };

    // Z3 fixedpoint format (declare-rel/rule/query) uses inverted sat/unsat polarity
    let fixedpoint = problem.is_fixedpoint_format();
    let (safe_str, unsafe_str) = if fixedpoint {
        ("unsat", "sat")
    } else {
        ("sat", "unsat")
    };

    // Compute time budget from global timeout (#2971)
    let timeout_ms = GLOBAL_TIMEOUT_MS.load(Ordering::Relaxed);
    let time_budget = if timeout_ms > 0 {
        portfolio_budget_from_timeout(Some(timeout_ms))
    } else {
        portfolio_budget_from_timeout(None)
    };

    // Trace mode runs a single validated PDR to produce a coherent trace file.
    // Without this, the adaptive portfolio may solve via synthesis (no PDR → no trace).
    let trace_enabled = env::var("Z4_TRACE_FILE")
        .map(|p| !p.trim().is_empty())
        .unwrap_or(false);
    let mut config = if trace_enabled {
        AdaptiveConfig::with_budget(time_budget, verbose).with_trace_mode(true)
    } else {
        AdaptiveConfig::with_budget(time_budget, verbose)
    };
    config.validate = validate;
    let progress = PROGRESS_ENABLED.load(Ordering::Relaxed);
    config.progress_enabled = progress;

    // Spawn background progress emitter if --progress is set.
    let progress_stop = if progress {
        Some(spawn_chc_progress_thread(solve_start))
    } else {
        None
    };

    let num_predicates = problem.predicates().len() as u64;
    let num_clauses = problem.clauses().len() as u64;
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();
    let chc_stats = solver.statistics();

    // Stop progress thread before printing result.
    if let Some(stop) = progress_stop {
        stop.store(true, Ordering::Relaxed);
    }

    let result_str = match &result {
        VerifiedChcResult::Safe(inv) => {
            safe_println!("{safe_str}");
            let cert = inv.model().to_certificate(solver.problem());
            safe_println!("{cert}");
            safe_str
        }
        VerifiedChcResult::Unsafe(cex) => {
            safe_println!("{unsafe_str}");
            let cert = cex.counterexample().to_certificate(solver.problem());
            safe_println!("{cert}");
            unsafe_str
        }
        VerifiedChcResult::Unknown(_) | _ => {
            exit_if_timed_out();
            safe_println!("unknown");
            safe_eprintln!("(:reason-unknown \"incomplete: CHC portfolio exhausted all strategies within budget\")");
            "unknown"
        }
    };
    if stats_cfg.any() {
        print_chc_stats(
            &solve_start,
            result_str,
            "portfolio",
            stats_cfg,
            Some(&chc_stats),
            num_predicates,
            num_clauses,
        );
    }
}

/// Run portfolio CHC solver on a file
///
/// Uses AdaptivePortfolio for intelligent strategy selection based on problem class.
pub(crate) fn run_portfolio(
    path: &str,
    verbose: bool,
    validate: bool,
    timeout_ms: Option<u64>,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    use z4::chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

    // proof_config accepted but not yet used for file output — certificates are
    // always printed to stdout after the sat/unsat line (#8152).
    let _ = proof_config;

    let solve_start = Instant::now();

    // Read and parse CHC file
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            safe_eprintln!("Error reading file: {}", e);
            return;
        }
    };

    let problem = match ChcParser::parse(&content) {
        Ok(p) => p,
        Err(e) => {
            safe_eprintln!("Parse error: {}", e);
            return;
        }
    };

    // Z3 fixedpoint format (declare-rel/rule/query) uses inverted sat/unsat polarity
    let fixedpoint = problem.is_fixedpoint_format();
    let (safe_str, unsafe_str) = if fixedpoint {
        ("unsat", "sat")
    } else {
        ("sat", "unsat")
    };

    let trace_enabled = env::var("Z4_TRACE_FILE")
        .map(|trace_path| !trace_path.trim().is_empty())
        .unwrap_or(false);

    // Configure adaptive portfolio
    let time_budget = portfolio_budget_from_timeout(timeout_ms);

    // Trace mode runs a single validated PDR to avoid multiple engines
    // clobbering the shared TLA trace file (#2585, #5811).
    let mut config = if trace_enabled {
        AdaptiveConfig::with_budget(time_budget, verbose).with_trace_mode(true)
    } else {
        AdaptiveConfig::with_budget(time_budget, verbose)
    };
    config.validate = validate;
    let progress = PROGRESS_ENABLED.load(Ordering::Relaxed);
    config.progress_enabled = progress;

    // Spawn background progress emitter if --progress is set.
    let progress_stop = if progress {
        Some(spawn_chc_progress_thread(solve_start))
    } else {
        None
    };

    let num_predicates = problem.predicates().len() as u64;
    let num_clauses = problem.clauses().len() as u64;
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();
    let chc_stats = solver.statistics();

    // Stop progress thread before printing result.
    if let Some(stop) = progress_stop {
        stop.store(true, Ordering::Relaxed);
    }

    let result_str = match &result {
        VerifiedChcResult::Safe(inv) => {
            safe_println!("{safe_str}");
            let cert = inv.model().to_certificate(solver.problem());
            safe_println!("{cert}");
            safe_str
        }
        VerifiedChcResult::Unsafe(cex) => {
            safe_println!("{unsafe_str}");
            let cert = cex.counterexample().to_certificate(solver.problem());
            safe_println!("{cert}");
            unsafe_str
        }
        VerifiedChcResult::Unknown(_) | _ => {
            exit_if_timed_out();
            safe_println!("unknown");
            safe_eprintln!("(:reason-unknown \"incomplete: CHC portfolio exhausted all strategies within budget\")");
            "unknown"
        }
    };
    if stats_cfg.any() {
        print_chc_stats(
            &solve_start,
            result_str,
            "portfolio",
            stats_cfg,
            Some(&chc_stats),
            num_predicates,
            num_clauses,
        );
    }
}

/// Calculate portfolio time budget accounting for elapsed time.
///
/// Uses 90% of remaining time to leave margin for printing results and process teardown.
pub(crate) fn portfolio_time_budget(timeout_ms: u64, elapsed: Duration) -> Duration {
    let elapsed_ms = u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX);
    let remaining_ms = timeout_ms.saturating_sub(elapsed_ms);
    // Use 95% of remaining time as budget. The 5% margin covers parsing,
    // setup, and teardown. CHC problems parse in <100ms so 90% was overly
    // conservative and left 1.5s unused on 15s benchmarks, causing near-
    // boundary problems (e.g., dillig02_m at ~14s) to time out.
    let budget_ms = u64::try_from((u128::from(remaining_ms) * 19) / 20).unwrap_or(u64::MAX);
    Duration::from_millis(budget_ms)
}

/// Compute the CHC portfolio budget from CLI timeout options.
///
/// Matches prior behavior:
/// - `Some(0)`: no internal timeout
/// - `Some(ms)`: 90% of remaining wall-clock timeout
/// - `None`: default 15s benchmark-aligned budget with teardown margin
pub(crate) fn portfolio_budget_from_timeout(timeout_ms: Option<u64>) -> Duration {
    match timeout_ms {
        Some(0) => Duration::ZERO,
        Some(ms) => {
            let elapsed = START_TIME.get().map(Instant::elapsed).unwrap_or_default();
            portfolio_time_budget(ms, elapsed)
        }
        None => portfolio_time_budget(15_000, Duration::ZERO),
    }
}

/// Minimum interval between CHC progress line emissions.
const CHC_PROGRESS_INTERVAL: Duration = Duration::from_secs(5);

/// Spawn a background thread that emits periodic CHC progress lines to stderr.
///
/// Returns a stop flag. Set it to `true` to terminate the progress thread.
/// The thread emits lines in DIMACS `c` comment format every 5 seconds:
///   `c [5.0s] CHC solving...`
fn spawn_chc_progress_thread(start: Instant) -> Arc<AtomicBool> {
    let stop = Arc::new(AtomicBool::new(false));
    let stop_clone = stop.clone();
    std::thread::Builder::new()
        .name("z4-chc-progress".to_string())
        .spawn(move || {
            loop {
                std::thread::sleep(CHC_PROGRESS_INTERVAL);
                if stop_clone.load(Ordering::Relaxed) {
                    break;
                }
                let elapsed = start.elapsed().as_secs_f64();
                let line = format!("c [{elapsed:.1}s] CHC portfolio solving...\n");
                let _ = Write::write_all(&mut std::io::stderr(), line.as_bytes());
            }
        })
        .ok();
    stop
}
