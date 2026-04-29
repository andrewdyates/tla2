// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Human-readable model-checking result reporting.

use anyhow::{bail, Result};
use tla_check::{CheckResult, ExplainedTrace};

use crate::cli_schema::TraceFormat;

use super::trace_format::{emit_liveness_trace, emit_trace, property_violation_presentation};
use super::{
    bytecode_vm_stats_line, format_configured_bounds, format_guard_suppression_suffix,
    print_storage_stats,
};

fn emit_bytecode_vm_stats_if_enabled(to_stderr: bool) {
    let Some(line) = bytecode_vm_stats_line() else {
        return;
    };
    if to_stderr {
        eprintln!("{line}");
    } else {
        println!("{line}");
    }
}

/// Print the standard statistics footer for human-readable output.
///
/// Used by the invariant, property, liveness, and deadlock arms (to stderr).
/// Prints states_found, initial_states, transitions, time, and storage stats.
/// The Error arm uses its own minimal inline stats (states_found + time only).
/// The Success and LimitReached arms use inline code for their extra fields.
fn emit_human_stats_footer(
    stats: &tla_check::CheckStats,
    elapsed: std::time::Duration,
    to_stderr: bool,
) {
    macro_rules! out {
        ($($arg:tt)*) => {
            if to_stderr { eprintln!($($arg)*); } else { println!($($arg)*); }
        }
    }
    out!("Statistics:");
    out!(
        "  States found: {}{}",
        stats.states_found,
        format_guard_suppression_suffix(stats.suppressed_guard_errors)
    );
    out!("  Initial states: {}", stats.initial_states);
    out!("  Transitions: {}", stats.transitions);
    out!("  Time: {:.3}s", elapsed.as_secs_f64());
    print_storage_stats(&stats.storage_stats, to_stderr);
}

/// Emit an explained trace annotation to stderr.
///
/// When `--explain-trace` is active, this prints a human-readable breakdown
/// of each state transition: what changed, which action fired, and a concise
/// summary per step.
fn emit_explained_trace(trace: &tla_check::Trace) {
    let explained = ExplainedTrace::from_trace(trace);
    eprintln!();
    eprint!("{}", explained);
}

/// Emit an explained liveness trace annotation to stderr.
fn emit_explained_liveness_trace(prefix: &tla_check::Trace, cycle: &tla_check::Trace) {
    let explained = ExplainedTrace::from_liveness_trace(prefix, cycle);
    eprintln!();
    eprint!("{}", explained);
}

/// Report model checking results in human-readable text format.
pub(crate) fn report_check_human(
    result: CheckResult,
    elapsed: std::time::Duration,
    max_states: usize,
    max_depth: usize,
    trace_format: TraceFormat,
    difftrace: bool,
    explain_trace: bool,
) -> Result<()> {
    match result {
        CheckResult::Success(stats) => {
            if let Some(bounds) = format_configured_bounds(max_states, max_depth) {
                println!(
                    "Model checking complete: No errors found within configured bounds ({}).",
                    bounds
                );
            } else {
                println!("Model checking complete: No errors found (exhaustive).");
            }
            println!();
            println!("Statistics:");
            println!(
                "  States found: {}{}",
                stats.states_found,
                format_guard_suppression_suffix(stats.suppressed_guard_errors)
            );
            println!("  Initial states: {}", stats.initial_states);
            println!("  Transitions: {}", stats.transitions);
            println!("  Max queue depth: {}", stats.max_queue_depth);
            if stats.phantom_dequeues > 0 {
                eprintln!(
                    "Warning: {} phantom dequeue(s) — fingerprint(s) dequeued but not in seen map",
                    stats.phantom_dequeues
                );
            }
            // Part of #2841: FP collision warnings (active in release builds when enabled).
            if stats.fp_dedup_collisions > 0 {
                eprintln!(
                    "Warning: {} TLC FP dedup collision(s) — same TLC fingerprint, different internal FP (potential over-exploration)",
                    stats.fp_dedup_collisions
                );
            }
            if stats.internal_fp_collisions > 0 {
                eprintln!(
                    "Warning: {} internal FP collision(s) — same internal FP, different TLC FP (potential under-exploration)",
                    stats.internal_fp_collisions
                );
            }
            println!("  Time: {:.3}s", elapsed.as_secs_f64());
            // Part of #3005: fingerprint collision probability estimate.
            let prob = stats.collision_probability();
            if prob > 0.0 {
                println!();
                println!(
                    "Fingerprint collision probability (optimistic): {}",
                    stats.collision_probability_string()
                );
            }
            // Collision detection results (when active).
            if stats.collision_check_mode.is_active() {
                println!();
                println!(
                    "{}",
                    tla_check::collision_detection::format_collision_report(
                        &stats.collision_check_stats,
                        stats.collision_check_mode,
                    )
                );
            }
            if !stats.detected_actions.is_empty() {
                println!();
                println!("Detected actions ({}):", stats.detected_actions.len());
                for action in &stats.detected_actions {
                    println!("  {}", action);
                }
            }
            // Part of #2665: storage backend stats (disk-tier activity or mmap
            // reserved-memory usage).
            print_storage_stats(&stats.storage_stats, false);
            if let Some(coverage) = stats.coverage.as_ref() {
                println!();
                println!("{}", coverage.format_report());
            }
            #[cfg(feature = "memory-stats")]
            tla_check::memory_stats::print_stats();
            emit_bytecode_vm_stats_if_enabled(false);
            Ok(())
        }
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            eprintln!("Error: Invariant {} is violated.", invariant);
            eprintln!("Error: The behavior up to this point is:");
            if trace.is_empty() {
                eprintln!("(trace unavailable: --no-trace mode)");
            } else {
                emit_trace(&trace, trace_format, difftrace, "Counterexample trace");
                if explain_trace {
                    emit_explained_trace(&trace);
                }
            }
            emit_human_stats_footer(&stats, elapsed, true);
            emit_bytecode_vm_stats_if_enabled(true);
            bail!("Invariant violation detected");
        }
        CheckResult::PropertyViolation {
            property,
            kind,
            trace,
            stats,
        } => {
            let presentation = property_violation_presentation(property.as_str(), kind);
            eprintln!("Error: {}", presentation.headline);
            eprintln!("Error: {}", presentation.trace_intro);
            if trace.is_empty() {
                eprintln!("(trace unavailable: --no-trace mode)");
            } else {
                emit_trace(&trace, trace_format, difftrace, "Counterexample trace");
                if explain_trace {
                    emit_explained_trace(&trace);
                }
            }
            emit_human_stats_footer(&stats, elapsed, true);
            emit_bytecode_vm_stats_if_enabled(true);
            bail!("Property violation detected");
        }
        CheckResult::LivenessViolation {
            property: _,
            prefix,
            cycle,
            stats,
        } => {
            eprintln!("Error: Temporal properties were violated.");
            eprintln!();
            eprintln!("Error: The following behavior constitutes a counter-example:");
            eprintln!();
            emit_liveness_trace(&prefix, &cycle, trace_format, difftrace);
            if explain_trace {
                emit_explained_liveness_trace(&prefix, &cycle);
            }
            emit_human_stats_footer(&stats, elapsed, true);
            emit_bytecode_vm_stats_if_enabled(true);
            bail!("Liveness violation detected");
        }
        CheckResult::Deadlock { trace, stats } => {
            eprintln!("Error: Deadlock reached.");
            eprintln!("Error: The behavior up to this point is:");
            if trace.is_empty() {
                eprintln!("(trace unavailable: --no-trace mode)");
            } else {
                emit_trace(&trace, trace_format, difftrace, "Trace to deadlock");
                if explain_trace {
                    emit_explained_trace(&trace);
                }
            }
            emit_human_stats_footer(&stats, elapsed, true);
            emit_bytecode_vm_stats_if_enabled(true);
            eprintln!();
            eprintln!("Hint: Use --no-deadlock to disable deadlock checking");
            bail!("Deadlock detected");
        }
        CheckResult::Error { error, stats, .. } => {
            eprintln!("Error: {}", error);
            eprintln!();
            eprintln!("Statistics:");
            eprintln!(
                "  States found: {}{}",
                stats.states_found,
                format_guard_suppression_suffix(stats.suppressed_guard_errors)
            );
            eprintln!("  Time: {:.3}s", elapsed.as_secs_f64());
            print_storage_stats(&stats.storage_stats, true);
            emit_bytecode_vm_stats_if_enabled(true);
            bail!("Model checking failed: {}", error);
        }
        CheckResult::LimitReached { limit_type, stats } => {
            let (limit_name, hint, known_limit) = match limit_type {
                tla_check::LimitType::States => (
                    "state",
                    "Use --max-states or --max-depth to adjust limits",
                    true,
                ),
                tla_check::LimitType::Depth => (
                    "depth",
                    "Use --max-states or --max-depth to adjust limits",
                    true,
                ),
                tla_check::LimitType::Exit => (
                    "exit (TLCSet)",
                    "Spec requested early termination via TLCSet(\"exit\", TRUE)",
                    true,
                ),
                tla_check::LimitType::Memory => {
                    ("memory", "Use --memory-limit to adjust the threshold", true)
                }
                tla_check::LimitType::Disk => {
                    ("disk", "Use --disk-limit to adjust the threshold", true)
                }
                _ => (
                    "unknown",
                    "Exploration limit reached; upgrade tla2 for limit details",
                    false,
                ),
            };
            println!("Model checking stopped: {} limit reached.", limit_name);
            if !known_limit {
                println!("Limit type: {:?}", limit_type);
                println!();
            }
            println!();
            println!("Statistics:");
            println!(
                "  States found: {}{}",
                stats.states_found,
                format_guard_suppression_suffix(stats.suppressed_guard_errors)
            );
            println!("  Initial states: {}", stats.initial_states);
            println!("  Transitions: {}", stats.transitions);
            println!("  Max depth: {}", stats.max_depth);
            println!("  Time: {:.3}s", elapsed.as_secs_f64());
            print_storage_stats(&stats.storage_stats, false);
            println!();
            println!("Hint: {}", hint);
            #[cfg(feature = "memory-stats")]
            tla_check::memory_stats::print_stats();
            emit_bytecode_vm_stats_if_enabled(false);
            Ok(())
        }
        _ => bail!(
            "Model checking produced a result variant unsupported by this tla2 version; upgrade tla2"
        ),
    }
}
